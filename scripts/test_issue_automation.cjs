// Exercise the actual inline workflow script, without GitHub access or a token.
const { readFileSync } = require('node:fs');
const { test } = require('node:test');
const assert = require('node:assert/strict');
const workflow = readFileSync(`${__dirname}/../.github/workflows/issue-automation.yml`, 'utf8');
const track = workflow.split('  track:\n')[1].split('\n  followups:')[0];
const script = track.split('          script: |\n')[1].split('\n  #')[0]
  .split('\n').map(line => line.startsWith('            ') ? line.slice(12) : line).join('\n');
const run = new (Object.getPrototypeOf(async function(){}).constructor)('github', 'context', 'core', script);

async function exercise(eventName, action, repository, options = {}) {
  const calls = [], logs = [];
  const parent = options.noParent ? null : {
    number: 10718, title: 'Tracker', state: 'OPEN',
    repository: repository === undefined ? undefined : { nameWithOwner: repository },
    labels: { nodes: [] },
  };
  const github = {
    graphql: async (query, vars) => {
      calls.push(['graphql', vars.n]);
      if (query.includes('parent {')) {
        assert.match(query, /repository\s*\{\s*nameWithOwner\s*\}/);
        if (options.lookupError) throw new Error('lookup unavailable');
        return { repository: { issue: { parent } } };
      }
      return { repository: { issue: { subIssues: { totalCount: 1, nodes: [{ state: 'CLOSED' }] } } } };
    },
    rest: { issues: Object.fromEntries(['listComments', 'createComment', 'addLabels', 'removeLabel'].map(method => [method, async args => {
      assert.equal(args.owner, 'LionSR');
      assert.equal(args.repo, 'QICLean');
      calls.push([method, args.issue_number]);
      return { data: [] };
    }])) },
  };
  const context = {
    repo: { owner: 'LionSR', repo: 'QICLean' }, eventName,
    payload: { action, issue: { number: 1050, title: 'Sites' },
      pull_request: { number: 1055, title: 'Sites', body: 'Addresses #1050', head: { ref: 'sites' } } },
  };
  await run(github, context, { info: x => logs.push(x), warning: x => logs.push(x) });
  return { calls, logs };
}
for (const [event, action] of [['issues', 'closed'], ['issues', 'reopened'], ['pull_request', 'opened'], ['pull_request', 'closed']]) {
  for (const remote of ['LionSR/TNLean', 'Other/QICLean', undefined]) {
    test(`${event}/${action} skips parent in ${remote}`, async () => {
      const { calls, logs } = await exercise(event, action, remote);
      assert.ok(logs.some(x => x.includes('skipping')));
      assert.deepEqual(calls.filter(x => x[1] === 10718), []);
      if (event === 'pull_request' && action === 'closed') {
        assert.ok(calls.some(x => x[0] === 'createComment' && x[1] === 1050));
      }
    });
  }
  test(`${event}/${action} keeps local tracking, case insensitive`, async () => {
    const { calls } = await exercise(event, action, 'lionsr/qiclean');
    assert.ok(calls.some(x => x[0] === 'createComment' && x[1] === 10718));
    if (event === 'issues' || action === 'closed') {
      assert.ok(calls.some(x => x[0] === 'addLabels' && x[1] === 10718));
    }
  });
}
for (const options of [{ noParent: true }, { lookupError: true }]) {
  test(`absent or unavailable parent is a safe no-op: ${JSON.stringify(options)}`, async () => {
    const { calls } = await exercise('issues', 'closed', 'LionSR/QICLean', options);
    assert.deepEqual(calls, [['graphql', 1050]]);
  });
}
