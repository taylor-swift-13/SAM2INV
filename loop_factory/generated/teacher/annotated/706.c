int main1(int k,int m,int n,int p){
  int b, c, e, v, x, l, j;

  b=60;
  c=0;
  e=p;
  v=2;
  x=-1;
  l=p;
  j=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c;
  loop invariant c <= b;
  loop invariant l == e + v + x || c == 0;
  loop invariant e == p;
  loop invariant p == \at(p, Pre);
  loop invariant (l == p) || (l == p+1);
  loop invariant v == 2;
  loop invariant x == -1;
  loop invariant b == 60;
  loop invariant (c == 0) || (l == e + v + x);
  loop invariant l == e + v + x || l == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (c == 0) ==> (l == p) && (c > 0) ==> (l == p + 1);
  loop assigns c, l;
*/
while (c+1<=b) {
      l = e+v+x;
      c = c+1;
  }

}
