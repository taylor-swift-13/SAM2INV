int main1(int a,int b,int k){
  int l, i, v;

  l=38;
  i=0;
  v=4;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant ((i == 0) ==> (v == 4)) && ((i > 0) ==> (v == 0));

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v-v;
      i = i+1;
  }

}