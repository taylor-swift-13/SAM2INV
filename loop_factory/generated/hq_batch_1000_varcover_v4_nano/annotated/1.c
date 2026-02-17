int main1(int a,int k,int m){
  int l, i, v;

  l=(k%12)+12;
  i=0;
  v=m;

  
  /*@

    loop invariant i % 5 == 0;

    loop invariant 0 <= i && i <= l + 4;

    loop invariant (i == 0 ==> v == \at(m, Pre)) && (i > 0 ==> (v == 0 || (v % 5 == 0 && v < l)));

    loop assigns i, v;

  */
while (i<l) {
      v = v-v;
      if (v+6<l) {
          v = v+i;
      }
      i = i+5;
  }

}