int main1(int a,int k,int n){
  int l, i, v;

  l=41;
  i=0;
  v=-5;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == -5);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v-v;
      v = v+i;
      v = v+v;
      i = i+1;
  }

}