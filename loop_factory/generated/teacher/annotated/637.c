int main1(int k,int q){
  int c, x, a, w, l, p;

  c=66;
  x=c+6;
  a=x;
  w=x;
  l=-4;
  p=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == x;
  loop invariant x == c + 6;
  loop invariant w >= x;
  loop invariant w >= c + 6;
  loop invariant w % a == 0;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant w >= a;
  loop invariant a != 0;
  loop invariant x >= c+1;
  loop invariant (w - x) % a == 0;
  loop invariant a > 0;
  loop assigns w;
*/
while (x>=c+1) {
      w = w+a;
  }

}
