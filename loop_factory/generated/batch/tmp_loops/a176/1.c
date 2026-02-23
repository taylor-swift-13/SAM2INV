int main1(int a,int p){
  int k, o, v, q;

  k=26;
  o=0;
  v=a;
  q=4;

  while (o+4<=k) {
      if (o<k/2) {
          v = v+q;
      }
      else {
          v = v+1;
      }
      v = v+q+q;
      v = v+1;
  }

}
