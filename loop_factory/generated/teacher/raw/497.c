int main1(int k,int m){
  int j, l, p;

  j=9;
  l=4;
  p=5;

  while (l+5<=j) {
      p = p+3;
      if (p+3<j) {
          p = p+p;
      }
      else {
          p = l%9;
      }
  }

}
