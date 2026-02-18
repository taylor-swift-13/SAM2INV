int main1(int a,int b,int m,int p){
  int l, i, v;

  l=25;
  i=l;
  v=l;

  
  /*@

    loop invariant l == 25;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant (i == l && v == l) || (i < l && v == m+3);

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= 25;

    loop invariant (i < 25) ==> v == m + 3;

    loop invariant m == \at(m, Pre) && a == \at(a, Pre) && b == \at(b, Pre) && p == \at(p, Pre);

    loop invariant (i == l && v == l) || (i < l && v == m + 3);

    loop invariant 0 <= i && i <= l;

    loop invariant (i == l) ==> v == l;

    loop invariant (i < l) ==> v == m + 3;

    loop invariant a == \at(a, Pre) && p == \at(p, Pre);

    loop invariant b == \at(b, Pre) && m == \at(m, Pre);

    loop assigns i, v;

  */
  while (i>0) {
      if (b<m+4) {
          v = v+i;
      }
      v = m-(-3);
      i = i-1;
  }

}