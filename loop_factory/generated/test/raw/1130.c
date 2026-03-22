int main1(int y,int v){
  int mek, p, c, ngg, crb;

  mek=v;
  p=mek;
  c=(v%40)+2;
  ngg=0;
  crb=v;

  while (c!=ngg) {
      ngg = c;
      c = (c+mek/c)/2;
      crb = (crb+ngg)+(-(c));
  }

  while (c!=crb) {
      crb = c;
      c = (c+mek/c)/2;
      p = p + mek;
  }

}
