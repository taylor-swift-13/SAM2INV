int main1(int b,int k){
  int p, q, v, r;

  p=(k%7)+8;
  q=0;
  v=p;
  r=q;

  while (1) {
      if (v+6<=p) {
          v = v+6;
      }
      else {
          v = p;
      }
  }

}
