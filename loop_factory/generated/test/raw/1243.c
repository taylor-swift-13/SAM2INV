int main1(){
  int f, ufzj, fj, ma, w9, uc, s;

  f=1;
  ufzj=0;
  fj=11;
  ma=f;
  w9=ufzj;
  uc=(1%6)+2;
  s=5;

  while (w9<=f-1) {
      fj = fj*uc+1;
      ma = ma*uc;
      s = s+(ma%9);
      uc = uc*3;
      w9 = f;
  }

}
