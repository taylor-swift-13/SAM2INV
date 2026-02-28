int main1(int k,int q){
  int g, t, b;

  g=18;
  t=0;
  b=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant g == 18;
  loop invariant b >= -5;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant t <= g;
  loop invariant -5 <= b;
  loop invariant b <= (b+4)*(b+5);
  loop invariant t <= g - 1;
  loop invariant b <= (b + 5) * (b + 4);
  loop assigns b;
*/
while (t+1<=g) {
      b = b+4;
      b = b*b+b;
  }

}
