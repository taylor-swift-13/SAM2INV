int main1(int k,int m,int n,int p){
  int l, i, v;

  l=p;
  i=0;
  v=0;

  
  /*@

    loop invariant i >= 0;


    loop invariant v == 0;

    loop invariant l == p;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant l == \at(p, Pre);

    loop invariant (l >= 0) ==> i <= l;

    loop assigns i, v;

  */
  while (i<l) {
      v = v+v;
      i = i+1;
  }

}