int main1(int a,int k){
  int v, r, g, p;

  v=(a%18)+14;
  r=v;
  g=-8;
  p=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == (a % 18) + 14;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p >= 0;
  loop invariant g <= g*g + g;
  loop invariant v == (\at(a, Pre) % 18) + 14;
  loop invariant (g > p) ==> (g - p) > 0;
  loop invariant (g <= p) ==> (p - g) >= 0;

  loop assigns g, p;
*/
while (g!=0&&p!=0) {
      if (g>p) {
          g = g-p;
      }
      else {
          p = p-g;
      }
      g = g*g+g;
  }

}
