int main1(int n,int l){
  int s, zp, ku, nmi, l16q, qj0, o, yead;

  s=n;
  zp=s;
  ku=0;
  nmi=1;
  l16q=0;
  qj0=s;
  o=s;
  yead=l;

  while (ku>=0&&ku<3) {
      if (!(!(ku==0&&nmi>=s))) {
          ku = 3;
      }
      else {
          if (ku==1&&l16q<nmi) {
              qj0 = qj0+nmi-l16q;
              l16q = l16q + 1;
          }
          else {
              if (ku==1&&l16q>=nmi) {
                  ku = 2;
              }
              else {
                  if (ku==2) {
                      nmi = nmi + 1;
                      ku = 0;
                  }
              }
          }
      }
      l = l+(zp%2);
      n += l16q;
      l = o+yead+n;
      o = o + 1;
  }

}
