int main96(int b,int k,int p){
  int h, s, v;

  h=41;
  s=0;
  v=h;

  while (s<h) {
      v = v+2;
      v = v+v;
  }


  /*@ assert s >= h; */
}
