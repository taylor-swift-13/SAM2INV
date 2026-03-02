int main1(int a,int q){
  int l, x, v;

  l=(a%30)+13;
  x=3;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - x*(x+1)/2 == a - 6;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x >= 3;
  loop invariant v >= a;
  loop invariant l == (\at(a,Pre) % 30) + 13;
  loop invariant v == a + ((x*x) + x - 12) / 2;
  loop invariant a == \at(a,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant 2*v == 2*a + x*x + x - 12;
  loop invariant l == (a % 30) + 13;
  loop invariant 2*(v - a) == x*x + x - 12;
  loop invariant v == a + (x*x + x - 12)/2;
  loop invariant l == (\at(a, Pre) % 30) + 13;
  loop invariant v == a + x*(x+1)/2 - 6;
  loop invariant l == (a%30) + 13;
  loop invariant 2*(v - \at(a, Pre)) == (x - 3) * (x + 4);
  loop invariant a == \at(a,Pre) && l == (\at(a,Pre) % 30) + 13 && q == \at(q,Pre);
  loop invariant v >= \at(a, Pre);
  loop invariant 2*v - x*x - x + 12 == 2*\at(a, Pre);
  loop invariant v == a + 4*(x - 3) + ((x - 3)*(x - 4))/2;
  loop assigns v, x;
*/
while (1) {
      v = v+1;
      v = v+x;
      x = x+1;
  }

}
