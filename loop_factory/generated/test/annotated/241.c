int main1(int m,int q){
  int l, i, v;

  l=39;
  i=l;
  v=q;

  
  /*@

    loop invariant i >= 0;

    loop invariant l == 39;

    loop invariant q == \at(q, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant (q >= 0) ==> (i * v <= 39 * q);

    loop invariant (q <= 0) ==> (i * v >= 39 * q);

    loop invariant i <= 39;


    loop invariant (q == 0) ==> (v == 0);

    loop invariant i <= l;

    loop invariant q == \at(q,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant (\at(q,Pre) >= 0) ==> i * v <= 39 * \at(q,Pre);

    loop invariant (\at(q,Pre) < 0)  ==> i * v >= 39 * \at(q,Pre);

    loop invariant (q >= 0) ==> (v >= 0);

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      v = v+v;
      i = i/2;
  }

}