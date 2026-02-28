int main1(int m,int q){
  int c, i, v, g;

  c=47;
  i=0;
  v=0;
  g=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g == c;
  loop invariant c == 47;

  loop invariant 2*v == i*(2*g+1);
  loop invariant v == 95 * (i / 2);
  loop invariant i % 2 == 0;
  loop invariant i <= c + 1;
  loop invariant i >= 0;
  loop invariant v == (2*g + 1) * (i / 2);
  loop assigns v, i;
*/
while (i<c) {
      v = v+g+g;
      v = v+1;
      i = i+2;
  }

}
