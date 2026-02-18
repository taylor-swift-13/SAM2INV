int main1(int k,int m,int n,int p){
  int l, i, v;

  l=m+10;
  i=0;
  v=-2;

  
  /*@

    loop invariant l == m + 10;

    loop invariant (l <= 0) || (i <= l);

    loop invariant (i == 0) ==> (v == -2);


    loop invariant v == -2 <==> i == 0;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant (v == -2) ==> (i == 0);

    loop invariant v <= 0;

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      if (i+4<=m+l) {
          v = v+1;
      }
      v = v-v;
      if (l<i+1) {
          v = v+1;
      }
      i = i+1;
  }

}