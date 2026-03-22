int main1(){
  int h, gzk, dom, b, l1;
  h=(1%60)+60;
  gzk=(1%9)+2;
  dom=0;
  b=0;
  l1=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= dom;
  loop invariant l1 == 12 + dom*(dom+1)/2;
  loop invariant h == (1%60) + 60;
  loop invariant gzk == (1%9) + 2;
  loop invariant b == 0;
  loop assigns b, dom, l1;
*/
while (h>gzk*dom+b) {
      if (!(!(b==gzk-1))) {
          b += 1;
      }
      else {
          b = 0;
          dom += 1;
      }
      l1 = l1+dom-b;
  }
}