int main1(int a,int p){
  int q, c, v;

  q=p-2;
  c=0;
  v=a;

  while (1) {
      v = v+3;
      if (q<p+2) {
          v = v+c;
      }
      else {
          v = v+1;
      }
  }

}
