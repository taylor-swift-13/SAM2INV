int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=p;

  while (v<n) {
      if (c+7<n) {
          c = c-n;
      }
      else {
          c = c+c;
      }
      v = v+1;
  }

}
