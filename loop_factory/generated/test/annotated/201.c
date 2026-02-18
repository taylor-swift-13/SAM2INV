int main1(int k,int m,int n,int p){
  int l, i, v;

  l=59;
  i=0;
  v=k;

  
  /*@

    loop invariant i <= l;

    loop invariant (i == 0) ==> v == k;

    loop invariant (i != 0) ==> v == 0;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant (i >= 1) ==> (v == 0);

    loop invariant (i == 0) ==> (v == \at(k, Pre));

    loop invariant (i > 0) ==> (v == 0);

    loop invariant (k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre));

    loop invariant l == 59;

    loop invariant 0 <= i && i <= l;

    loop invariant (i == 0 && v == k) || (i > 0 && v == 0);

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant i >= 0;

    loop invariant i > 0 ==> v == 0;

    loop invariant i == 0 || v == 0;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%9)==0) {
          v = v+3;
      }
      v = v+v;
      v = v-v;
      i = i+1;
  }

}