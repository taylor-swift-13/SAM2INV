int main1(int a,int b){
  int l, i, v;

  l=b+4;
  i=l;
  v=l;

  
  /*@

    loop invariant l == \at(b, Pre) + 4;

    loop invariant b == \at(b, Pre);

    loop invariant a == \at(a, Pre);


    loop invariant v == 0 || v == i;

    loop invariant l == b + 4;

    loop invariant i <= l;


    loop invariant v <= i;

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = i;
      v = v-v;
      i = i-1;
  }

}