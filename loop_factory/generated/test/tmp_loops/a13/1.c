int main1(int a,int b){
  int l, i, v;

  l=a-2;
  i=l;
  v=-5;

  while (i>0) {
      v = v+v;
      i = i-1;
  }

  while (v<i) {
      v = v+1;
  }

}
