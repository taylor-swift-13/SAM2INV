int main1(int s,int t){
  int qp, o6, o, jpu;

  qp=t;
  o6=0;
  o=s;
  jpu=0;

  while (1) {
      if (!(o6<qp)) {
          break;
      }
      o6 += 2;
      if (jpu<=o) {
          o = jpu;
      }
      s = s+o6-o6;
  }

}
