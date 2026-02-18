int main1(int a,int m,int p,int q){
  int l, i, v;

  l=11;
  i=l;
  v=2;

  
  /*@

    loop invariant l == 11;

    loop invariant 0 <= i && i <= l;

    loop invariant (a == \at(a, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre));

    loop invariant v == 0 || v == 2;

    loop invariant i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= v && v <= 2;

    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop invariant (i < l) ==> (v == 0);

    loop invariant 0 <= i && i <= 11;

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v-v;
      if ((i%3)==0) {
          v = v-i;
      }
      v = v%3;
      i = i-1;
  }

}