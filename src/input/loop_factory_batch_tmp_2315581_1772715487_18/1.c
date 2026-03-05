int main1(){
  int v1d9, juc, d3zy, zd;

  v1d9=1;
  juc=0;
  d3zy=7;
  zd=0;

  while (juc<v1d9) {
      zd = juc%5;
      if (juc>=d3zy) {
          d3zy = (juc-d3zy)%5;
          d3zy = d3zy+zd-d3zy;
      }
      else {
          d3zy += zd;
      }
      d3zy = d3zy+zd+zd;
      juc++;
  }

}
