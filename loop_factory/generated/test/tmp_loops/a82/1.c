int main1(int b,int m){
  int l, i, v;

  l=(m%39)+14;
  i=0;
  v=-6;

  while (i<l) {
      v = v+v;
      i = i+1;
  }

  while (i>0) {
      i = i-1;
  }

}
