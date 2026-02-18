int main1(int k,int m,int p,int q){
  int l, i, v;

  l=26;
  i=l;
  v=5;

  
  /*@

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == 26;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant 0 <= i <= 26;


    loop invariant 0 <= i && i <= 26;


    loop invariant v % 5 == 0;

    loop invariant i <= 26;

    loop assigns i, v;

  */
while (i>0) {
      if ((i%5)==0) {
          v = v+i;
      }
      i = i-1;
  }

}