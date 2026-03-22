int main1(int c){
  int g2, u6, v9, el, js, wn;
  g2=c*3;
  u6=c+5;
  v9=g2;
  el=c;
  js=(c%6)+2;
  wn=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g2 == 3 * c;
  loop invariant (el >= c) && ((c >= 0) ==> (el <= g2)) && ((c < 0) ==> (el >= g2));
  loop assigns u6, v9, el, js, wn;
*/
while (1) {
      if (el>=g2) {
          break;
      }
      u6 = u6*js+c;
      v9 = v9*js;
      el += 1;
      js = js + el;
      js = js*4+3;
      wn = wn*js+3;
  }
}