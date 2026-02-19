int main1(int m,int n){
  int l, i, v, u;

  l=(m%28)+20;
  i=l;
  v=4;
  u=m;

  
  /*@

    loop invariant i == l;

    loop invariant l == (\at(m, Pre) % 28) + 20;

    loop invariant i >= -7;

    loop invariant i <= 47;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant v >= 0;

    loop invariant v >= 4;

    loop invariant (v > 4) ==> (u % 2 == 0);




    loop invariant -7 <= i && i <= 47;


    loop assigns v, u;

  */
  while (i>0) {
      v = v+1;
      u = u+1;
      u = u+u;
  }

  /*@
  loop invariant i == l;
  loop invariant l == (\at(m, Pre) % 28) + 20;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= 0;
  loop assigns u, v;
  */
  while (v<i) {
      u = u+l+l;
      u = u+1;
      v = v*2;
  }

}