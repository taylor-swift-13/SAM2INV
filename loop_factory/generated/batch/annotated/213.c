int main1(int m,int p){
  int h, o, l;

  h=p;
  o=0;
  l=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant (l == -5 || l == 0) && p == \at(p, Pre);
  loop invariant h == \at(p, Pre);

  loop invariant (l == -5) || (-4 <= l && l <= 4);
  loop invariant h == p;
  loop invariant 0 <= o;
  loop invariant l <= 0;
  loop invariant (l == -5) || (l == 0);
  loop invariant l % 5 == 0;
  loop invariant o >= 0;
  loop invariant o <= h || h < 0;

  loop invariant (o == 0) ==> (l == -5);
  loop assigns o, l;
*/
while (o<h) {
      l = l%5;
      o = o+1;
  }

}
