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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l16q <= nmi;
  loop invariant zp == s;
  loop invariant qj0 >= s;
  loop invariant o >= s;
  loop invariant s == \at(n, Pre);
  loop invariant n >= \at(n, Pre);
  loop invariant nmi >= 1;
  loop invariant yead == \at(l, Pre);
  loop invariant 0 <= ku;
  loop invariant ku <= 3;
  loop assigns ku, l, l16q, n, nmi, o, qj0;
*/
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