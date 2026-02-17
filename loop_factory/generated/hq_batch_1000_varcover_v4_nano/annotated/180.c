int main1(int m,int n,int p){
  int l, i, v;

  l=p;
  i=l;
  v=l;

  
  /*@

    loop invariant l == \at(p, Pre);

    loop invariant i <= l;

    loop invariant (l > 0) ==> (0 <= i);

    loop invariant (i == l) ==> v == l;

    loop invariant (i < l) ==> v == 0;

    loop assigns v, i;

  */
while (i>0) {
      v = v-v;
      v = v+3;
      if ((i%4)==0) {
          v = v-v;
      }
      v = v-v;
      v = v-v;
      i = i-1;
  }

}