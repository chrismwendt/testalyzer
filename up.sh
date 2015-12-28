pipe=/tmp/pipe
rm -rf $pipe
mkfifo $pipe

stack ghci < $pipe &

(
while inotifywait -e close_write src/* *.txt 2>/dev/null >/dev/null; do
    echo ':r'
    echo 'main'
done
) >$pipe
