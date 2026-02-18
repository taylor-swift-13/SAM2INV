int main1(int k,int m,int p,int q){
  int l, i, v, e, y;

  l=70;
  i=0;
  v=5;
  e=2;
  y=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant (k < q + 5) ==> (v == 5 + 2*i);
    loop invariant (k < q + 5) ==> (e == 2 + i*i + 5*i);
    loop invariant (k < q + 5) ==> (0 <= i && i <= l);
    loop invariant !(k < q + 5) ==> (v == 5 + 7*i);
    loop invariant !(k < q + 5) ==> (y == m);
    loop invariant 0 <= i <= l;
    loop invariant 5 <= v && v <= 5 + 7*i;
    loop invariant e >= 2;
    loop invariant y >= m;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l;
    loop invariant v >= 5 + 2*i;
    loop invariant i >= 0;
    loop invariant v >= 5;
    loop invariant v <= 5 + 7*i;
    loop invariant e <= 2 + 6*i + 7*(i*(i-1))/2;
    loop invariant y <= m + (i*(i-1))/2;
    loop invariant l == 70;
    loop invariant (k >= q + 5) ==> (v == 5 + 7*i);
    loop invariant (k >= q + 5) ==> (y == m);
    loop invariant e >= i*i + 5*i + 2;
    loop invariant e <= (7*i*i + 5*i + 4)/2;
    loop invariant y <= m + i*(i-1)/2;
    loop assigns v, e, y, i;
  */
while (i<l) {
      v = v+1;
      e = e+v;
      if (k<q+5) {
          y = y+i;
      }
      else {
          v = v+5;
      }
      v = v+1;
      i = i+1;
  }

}