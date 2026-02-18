int main1(int b,int k,int m,int q){
  int l, i, v;

  l=q;
  i=0;
  v=m;

  
  /*@

    loop invariant l == q;

    loop invariant 0 <= i;

    loop invariant i <= l || l < 0;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == \at(q, Pre);

    loop invariant i >= 0;


    loop invariant (i == 0) ==> v == \at(m, Pre);

    loop invariant (i != 0) ==> ( ((i - 1) < 12) ==> v == 0 ) && ( ((i - 1) >= 12) ==> v == (i - 1) + 8 );

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = 8;
      if (i<v+4) {
          v = v-v;
      }
      else {
          v = v+i;
      }
      i = i+1;
  }

}