int main1(int x,int e){
  int jk86, l6s, a, ck, ij6k, cxu, e3, ad;

  jk86=48;
  l6s=0;
  a=11;
  ck=0;
  ij6k=l6s;
  cxu=e;
  e3=0;
  ad=x;

  while (l6s<jk86) {
      if (l6s%2==0) {
          if (a>0) {
              a -= 1;
              ck += 1;
          }
      }
      else {
          if (ck>0) {
              ck = ck - 1;
              a++;
          }
      }
      cxu = cxu + 1;
      e3 = e3 + jk86;
      ij6k += 2;
      l6s++;
      cxu--;
      ij6k = ij6k + 1;
      if (e3+5<jk86) {
          cxu = ad-cxu;
      }
  }

}
