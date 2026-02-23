int main1(int n,int p){
  int t, i, v, w;

  t=(n%14)+9;
  i=t;
  v=n;
  w=-1;

  while (i>0) {
      if (v+2<=t) {
          v = v+2;
      }
      else {
          v = t;
      }
      v = v+w+w;
      v = v+1;
  }

}
