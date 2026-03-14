int main1(int x){
  int cxe, mkg, c, p;

  cxe=(x%40)+11;
  mkg=cxe;
  c=mkg;
  p=x;

  while (c<cxe) {
      c = c + 1;
      p = p + c;
      x += 2;
  }

}
