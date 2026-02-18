int main1(int k,int m,int n,int p){
  int l, i, v, u;

  l=9;
  i=l;
  v=8;
  u=-5;

  
  /*@

    loop invariant i >= 0;

    loop invariant l == 9;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i && i <= l;


    loop invariant (i == l && v == 8 && u == -5) || (v == m + i + 1);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant ((i == l && v == 8) || (i < l && v == m + i + 1));

    loop assigns i, v, u;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      u = u-1;
      v = v+1;
      v = v+i;
      if ((i%9)==0) {
          u = u+4;
      }
      else {
          v = u-v;
      }
      if (i+2<=i+l) {
          v = m+i;
      }
      i = i-1;
  }

}