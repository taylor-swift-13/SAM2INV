int main1(int w){
  int cm7, au8, c, dw, v;

  cm7=w;
  au8=0;
  c=au8;
  dw=11;
  v=au8;

  while (au8 < cm7) {
      au8 = (c--, dw--, v--, au8 + 1);
      dw = dw + 3;
      c += v;
      v = v + 3;
  }

}
