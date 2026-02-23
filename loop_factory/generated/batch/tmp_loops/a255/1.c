int main1(int a,int p){
  int h, o, v, l;

  h=44;
  o=0;
  v=3;
  l=h;

  while (o+3<=h) {
      if (o<h/2) {
          v = v+l;
      }
      else {
          v = v+1;
      }
      v = v+1;
      l = l+v;
  }

}
