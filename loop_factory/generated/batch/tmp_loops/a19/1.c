int main1(int a,int m){
  int p, w, c, o;

  p=(m%11)+9;
  w=p;
  c=p;
  o=3;

  while (w>=1) {
      if (c+5<=p) {
          c = c+5;
      }
      else {
          c = p;
      }
  }

}
