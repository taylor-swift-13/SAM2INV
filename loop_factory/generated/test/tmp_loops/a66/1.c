int main1(int b,int n){
  int l, i, v, g;

  l=b+7;
  i=l;
  v=l;
  g=b;

  while (i>0) {
      v = v+g+g;
      v = v+1;
      i = i-1;
  }

  while (l>0) {
      i = i+1;
      v = v-1;
  }

}
