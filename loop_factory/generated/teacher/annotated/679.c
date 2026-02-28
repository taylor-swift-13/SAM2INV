int main1(int b,int k,int n,int q){
  int v, i, o, w, p, e, y;

  v=k-2;
  i=0;
  o=2;
  w=-3;
  p=k;
  e=-5;
  y=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o % 2 == 0;
  loop invariant o >= 2;
  loop invariant w == (o*o + o - 12) / 2;
  loop invariant 2*w == o*o + o - 12;
  loop invariant v == k - 2;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns o, w;
*/
while (1) {
      o = o+1;
      w = w+o;
      o = o+1;
      w = w+o;
  }

}
