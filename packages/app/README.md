This is a [Next.js](https://nextjs.org/) project bootstrapped with [`create-next-app`](https://github.com/vercel/next.js/tree/canary/packages/create-next-app).

## Getting Started

Install the [vercel CLI](https://vercel.com/docs/cli).

Link local repo to vercel project: (select scope `Gnosis Guild` and confirm project `zodiac-roles-app`)

```bash
vercel link -p zodiac-roles-app
```

Set up local env vars (for connecting to KV store):

```bash
vercel env pull .env.development.local
```

Install dependencies, run code generation jobs, and start the development server by running the following commands in the repository root directory:

```bash
yarn
yarn prepare
yarn dev
```

Open [http://localhost:3000](http://localhost:3000) with your browser to see the result.

## SDK version

The app uses the **published** `zodiac-roles-sdk` from npm (`"zodiac-roles-sdk": "npm:^4.1.3"` in `package.json`), not the SDK in `packages/sdk`. The local SDK gets breaking changes for Roles v3, while the 4.x line keeps being published from [zodiaceco/zodiac-modifier-roles-v2](https://github.com/zodiaceco/zodiac-modifier-roles-v2).

The `npm:` protocol, together with `enableTransparentWorkspaces: false` in `.yarnrc.yml`, keeps Yarn from linking the local workspace. To move to a newer release, change the range and run `yarn` in the repo root.

## Learn More

To learn more about Next.js, take a look at the following resources:

- [Next.js Documentation](https://nextjs.org/docs) - learn about Next.js features and API.
- [Learn Next.js](https://nextjs.org/learn) - an interactive Next.js tutorial.\
- [Next.js deployment documentation](https://nextjs.org/docs/deployment)

You can check out [the Next.js GitHub repository](https://github.com/vercel/next.js/) - your feedback and contributions are welcome!
