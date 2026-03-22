int main1(){
  int n4ls, mi, ux9, wdn, ygc;
  n4ls=54;
  mi=n4ls;
  ux9=0;
  wdn=0;
  ygc=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ygc == wdn + 10*ux9 - 1;
  loop invariant 0 <= wdn <= 9;
  loop invariant ux9 >= 0;
  loop invariant wdn == (mi - n4ls) % 10;
  loop invariant ux9 == (mi - n4ls) / 10;
  loop assigns wdn, ygc, ux9, mi;
*/
while (1) {
      if (!(mi<=n4ls-1)) {
          break;
      }
      wdn += 1;
      ygc += 1;
      if (wdn>=10) {
          wdn = wdn - 10;
          ux9 = ux9 + 1;
      }
      mi++;
  }
}