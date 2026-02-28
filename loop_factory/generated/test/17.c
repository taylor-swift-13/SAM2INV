int main17(int a,int m,int p){
  int b, o, v;

  b=54;
  o=b;
  v=-2;

  while (o>0) {
      v = v+o;
      v = v-v;
      if (v<o+1) {
          v = v+2;
      }
      v = v+v;
      o = o-1;
  }

  while (1) {
      o = o+2;
      o = o*o;
      if (v+5<=p+b) {
          o = o+o;
      }
      o = o+v;
      o = o*2;
  }


  /*@ assert \false; */
}
