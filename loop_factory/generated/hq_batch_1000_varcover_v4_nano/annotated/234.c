int main1(int k,int n,int q){
  int l, i, v, b, f, w, c, g;

  l=40;
  i=l;
  v=k;
  b=q;
  f=-3;
  w=l;
  c=l;
  g=0;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant f == -3 + 2*(l - i);

    loop invariant ((l - i) % 2 == 0) ==> v == \at(k,Pre);

    loop invariant ((l - i) % 2 != 0) ==> v == -\at(k,Pre) - 4;

    loop invariant k == \at(k,Pre);

    loop assigns v, f, i;

    loop variant i;

  */
while (i>0) {
      v = v+4;
      f = f+2;
      v = g-v;
      i = i-1;
  }

}