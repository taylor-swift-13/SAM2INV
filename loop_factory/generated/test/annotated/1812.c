int main1(){
  int u6, x7p, e, o5, zds;
  u6=(1%8)+18;
  x7p=0;
  e=0;
  o5=11;
  zds=x7p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == 0;
  loop invariant o5 == 11;
  loop invariant zds == 0;
  loop invariant (0 <= x7p);
  loop invariant (x7p <= u6);
  loop invariant u6 == 19;
  loop assigns e, o5, x7p, zds;
*/
while (1) {
      if (!(x7p < u6)) {
          break;
      }
      e = e * ((x7p % 2) + 1);
      o5 = o5 + e;
      x7p += 1;
      zds = (zds+e)%6;
  }
}