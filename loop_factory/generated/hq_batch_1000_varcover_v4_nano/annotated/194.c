int main1(int b,int m,int p){
  int l, i, v, y, e;

  l=14;
  i=0;
  v=m;
  y=m;
  e=p;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == m + i*(m + p);

    loop invariant y == m;

    loop invariant e == p;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+y+e;
      i = i+1;
  }

}