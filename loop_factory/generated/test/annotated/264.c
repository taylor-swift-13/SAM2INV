int main1(int m,int n){
  int l, i, v;

  l=29;
  i=0;
  v=-3;

  
  /*@

    loop invariant l == 29;

    loop invariant m == \at(m,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == -3);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i <= l;


    loop invariant i >= 0;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%8)==0) {
          v = v+1;
      }
      else {
          v = m-l;
      }
      i = i+1;
  }

}