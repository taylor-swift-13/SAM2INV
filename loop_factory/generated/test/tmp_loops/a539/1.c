int main1(int a,int b){
  int l, i, v, z;

  l=a+20;
  i=l;
  v=-1;
  z=l;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (v>0) {
      i = i+1;
      i = i-v;
      v = v-1;
  }

}
