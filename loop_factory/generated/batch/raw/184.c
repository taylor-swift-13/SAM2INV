int main1(int b,int m){
  int a, i, v;

  a=m;
  i=a;
  v=a;

  while (i>=2) {
      if (i+4<=v+a) {
          v = v+v;
      }
      else {
          v = v+i;
      }
      v = i;
      i = i-2;
  }

}
