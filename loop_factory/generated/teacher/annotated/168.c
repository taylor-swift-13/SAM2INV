int main1(int a,int q){
  int h, c, v;

  h=35;
  c=2;
  v=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == h + c - 2;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant c <= h;
  loop invariant v - h == c - 2;
  loop invariant c >= 2;
  loop invariant v == c + 33;
  loop invariant 2 <= c;
  loop invariant h >= 6;
  loop invariant v <= h + c - 2;
  loop invariant v >= h;
  loop invariant h == 35;
  loop assigns v, c;
*/
while (c<=h-1) {
      if (c+7<=h+h) {
          v = v+1;
      }
      c = c+1;
  }

}
