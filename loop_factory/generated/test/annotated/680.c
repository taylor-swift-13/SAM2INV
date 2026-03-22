int main1(){
  int jg, p, h, sa6o, o;
  jg=1+9;
  p=jg;
  h=(1%40)+2;
  sa6o=0;
  o=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 10;
  loop invariant sa6o >= 0;
  loop invariant jg == 10;
  loop invariant h == 3;
  loop invariant sa6o <= h;
  loop assigns sa6o, h, o;
*/
while (1) {
      if (!(h!=sa6o)) {
          break;
      }
      sa6o = h;
      h = (h+jg/h)/2;
      o = o+h-h;
  }
}