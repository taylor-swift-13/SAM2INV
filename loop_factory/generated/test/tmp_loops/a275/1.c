int main1(int a,int m){
  int l, i, v, f;

  l=a+9;
  i=0;
  v=-3;
  f=i;

  while (i<l) {
      v = v+1;
      f = f-1;
      i = i+3;
  }

  while (f<i) {
      v = v+a;
      v = v-v;
      f = f+1;
  }

}
