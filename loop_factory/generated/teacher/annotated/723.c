int main1(int a,int m,int n,int q){
  int o, r, p, j, v, i, w, c;

  o=m+4;
  r=0;
  p=r;
  j=o;
  v=-1;
  i=5;
  w=r;
  c=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 5;
  loop invariant o == m + 4;
  loop invariant p == 0;
  loop invariant v == -1;
  loop invariant w == 0 || w == i - 1;
  loop invariant j <= o;
  loop invariant p == 0 && v == -1 && r == 0 && o == m + 4 && i == 5 && (w == 0 || w == i - 1) && j <= o;
  loop invariant 0 <= w;
  loop invariant w <= i - 1;
  loop invariant o == \at(m, Pre) + 4;
  loop invariant p == r;
  loop invariant w == 0 || w == 4;
  loop invariant (w == 0) || (w == i - 1);
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns j, v, w;
*/
while (1) {
      j = j+v;
      v = v+p;
      w = w+1;
      if (p+2<o) {
          j = j+r;
      }
      w = i-w;
      r = r;
  }

}
